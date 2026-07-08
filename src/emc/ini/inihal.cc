
/*----------------------------------------------------------------------
This work derived from alex joni's halui.cc
Copyright: 2013,2014
Author:    Dewey Garrett <dgarrett@panix.com>

This program is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
----------------------------------------------------------------------*/
#include "rcs_print.hh"
#include "emc.hh"
#include "emcglb.h"
#include <stdio.h>
#include "hal.h"
#include "rtapi.h"
#include "inihal.hh"
#include "iniaxis.hh"
#include "inispindle.hh"

static int debug=0;
static int comp_id;
extern value_inihal_data old_inihal_data;

static ptr_inihal_data *the_inihal_data;

#define PREFIX "ini."
#define EPSILON .00001
#define CLOSE(a,b,eps) ((a)-(b) < +(eps) && (a)-(b) > -(eps))

#define NEW(NAME) new_inihal_data.NAME

#define CHANGED(NAME) \
    ((old_inihal_data.NAME) - (new_inihal_data.NAME) > +(EPSILON)) \
    || \
    ((old_inihal_data.NAME) - (new_inihal_data.NAME) < -(EPSILON))

#define CHANGED_IDX(NAME,IDX) \
    ((old_inihal_data.NAME[IDX]) - (new_inihal_data.NAME[IDX]) > +(EPSILON)) \
    || \
    ((old_inihal_data.NAME[IDX]) - (new_inihal_data.NAME[IDX]) < -(EPSILON))

#define UPDATE(NAME) old_inihal_data.NAME = new_inihal_data.NAME

#define UPDATE_IDX(NAME,IDX) old_inihal_data.NAME[IDX] = new_inihal_data.NAME[IDX]

#define SHOW_CHANGE(NAME) \
    fprintf(stderr,"Changed: "#NAME" %g-->%g\n",old_inihal_data.NAME, \
                                                new_inihal_data.NAME);
#define SHOW_CHANGE_ARC_BLEND() \
    fprintf(stderr,"Changed: blend_enable:          %d-->%d\n"\
                   "         blend_fallback_enable: %d-->%d\n"\
                   "         optimization_depth:    %d-->%d\n"\
                   "         gap_cycles:            %f-->%f\n"\
                   "         ramp_freq:             %f-->%f\n"\
           ,old_inihal_data.traj_arc_blend_enable \
           ,new_inihal_data.traj_arc_blend_enable \
           ,old_inihal_data.traj_arc_blend_fallback_enable \
           ,new_inihal_data.traj_arc_blend_fallback_enable \
           ,old_inihal_data.traj_arc_blend_optimization_depth \
           ,new_inihal_data.traj_arc_blend_optimization_depth \
           ,old_inihal_data.traj_arc_blend_gap_cycles \
           ,new_inihal_data.traj_arc_blend_gap_cycles \
           ,old_inihal_data.traj_arc_blend_ramp_freq \
           ,new_inihal_data.traj_arc_blend_ramp_freq \
          );

#define SHOW_CHANGE_IDX(NAME,IDX) \
    fprintf(stderr,"Changed: "#NAME"[%d] %g-->%g\n",IDX,old_inihal_data.NAME[IDX], \
                                                        new_inihal_data.NAME[IDX]);
#define SHOW_CHANGE_IDX_INT(NAME,IDX) \
    fprintf(stderr,"Changed: "#NAME"[%d] %d-->%d\n",IDX,old_inihal_data.NAME[IDX], \
                                                        new_inihal_data.NAME[IDX]);
#define MAKE_BIT_PIN(NAME,DIR) \
do { \
     retval = hal_pin_bit_newf(DIR,&(the_inihal_data->NAME),comp_id,PREFIX#NAME); \
     if (retval < 0) return retval; \
   } while (0)

#define MAKE_S32_PIN(NAME,DIR) \
do { \
     retval = hal_pin_s32_newf(DIR,&(the_inihal_data->NAME),comp_id,PREFIX#NAME); \
     if (retval < 0) return retval; \
   } while (0)

#define MAKE_S32_PIN_IDX(NAME,HALPIN_NAME,DIR,IDX) \
do { \
     retval = hal_pin_s32_newf(DIR,&(the_inihal_data->NAME[IDX]),\
                               comp_id,PREFIX"%d."#HALPIN_NAME,IDX); \
     if (retval < 0) return retval; \
   } while (0)

#define MAKE_FLOAT_PIN(NAME,DIR) \
do { \
     retval = hal_pin_float_newf(DIR,&(the_inihal_data->NAME),comp_id,PREFIX#NAME); \
     if (retval < 0) return retval; \
   } while (0)

#define MAKE_FLOAT_PIN_IDX(NAME,HALPIN_NAME,DIR,IDX) \
do {                        \
     retval = hal_pin_float_newf(DIR,&(the_inihal_data->NAME[IDX]),\
                                 comp_id,PREFIX"%d."#HALPIN_NAME,IDX); \
     if (retval < 0) return retval; \
   } while (0)

#define MAKE_FLOAT_PIN_LETTER(NAME,HALPIN_NAME,DIR,IDX,LETTER) \
do {                        \
     retval = hal_pin_float_newf(DIR,&(the_inihal_data->NAME[IDX]),\
                                 comp_id,PREFIX"%c."#HALPIN_NAME,LETTER); \
     if (retval < 0) return retval; \
   } while (0)

#define INIT_PIN(NAME) *(the_inihal_data->NAME) = old_inihal_data.NAME;

int ini_hal_exit(void)
{
    hal_exit(comp_id);
    comp_id = -1;
    return 0;
}

int ini_hal_init(int numjoints)
{
    int retval;

    comp_id = hal_init("inihal");
    if (comp_id < 0) {
    rtapi_print_msg(RTAPI_MSG_ERR,
            "ini_hal_init: ERROR: hal_init() failed\n");
    return -1;
    }

    the_inihal_data = (ptr_inihal_data *) hal_malloc(sizeof(ptr_inihal_data));
    if (the_inihal_data == 0) {
        rtapi_print_msg(RTAPI_MSG_ERR,
                       "ini_hal_init: ERROR: hal_malloc() failed\n");
        hal_exit(comp_id);
        return -1;
    }

    for (int idx = 0; idx < numjoints; idx++) {
        MAKE_FLOAT_PIN_IDX(joint_backlash,backlash,HAL_IN,idx);
        MAKE_FLOAT_PIN_IDX(joint_ferror,ferror,HAL_IN,idx);
        MAKE_FLOAT_PIN_IDX(joint_min_ferror,min_ferror,HAL_IN,idx);
        MAKE_FLOAT_PIN_IDX(joint_min_limit,min_limit,HAL_IN,idx);
        MAKE_FLOAT_PIN_IDX(joint_max_limit,max_limit,HAL_IN,idx);
        MAKE_FLOAT_PIN_IDX(joint_max_velocity,max_velocity,HAL_IN,idx);
        MAKE_FLOAT_PIN_IDX(joint_max_acceleration,max_acceleration,HAL_IN,idx);
        MAKE_FLOAT_PIN_IDX(joint_home,home,HAL_IN,idx);
        MAKE_FLOAT_PIN_IDX(joint_home_offset,home_offset,HAL_IN,idx);
        MAKE_S32_PIN_IDX(  joint_home_sequence,home_sequence,HAL_IN,idx);
    }
    for (int idx = 0; idx < EMCMOT_MAX_AXIS; idx++) {
        char letter = "xyzabcuvw"[idx];
        MAKE_FLOAT_PIN_LETTER(axis_min_limit,min_limit,HAL_IN,idx,letter);
        MAKE_FLOAT_PIN_LETTER(axis_max_limit,max_limit,HAL_IN,idx,letter);
        MAKE_FLOAT_PIN_LETTER(axis_max_velocity,max_velocity,HAL_IN,idx,letter);
        MAKE_FLOAT_PIN_LETTER(axis_max_acceleration,max_acceleration,HAL_IN,idx,letter);
    }

    MAKE_FLOAT_PIN(traj_default_velocity,HAL_IN);
    MAKE_FLOAT_PIN(traj_max_velocity,HAL_IN);
    MAKE_FLOAT_PIN(traj_default_acceleration,HAL_IN);
    MAKE_FLOAT_PIN(traj_max_acceleration,HAL_IN);

    MAKE_BIT_PIN(traj_arc_blend_enable,HAL_IN);
    MAKE_BIT_PIN(traj_arc_blend_fallback_enable,HAL_IN);
    MAKE_S32_PIN(traj_arc_blend_optimization_depth,HAL_IN);
    MAKE_FLOAT_PIN(traj_arc_blend_gap_cycles,HAL_IN);
    MAKE_FLOAT_PIN(traj_arc_blend_ramp_freq,HAL_IN);
    MAKE_FLOAT_PIN(traj_arc_blend_tangent_kink_ratio,HAL_IN);

    hal_ready(comp_id);
    return 0;
} // ini_hal_init()

int ini_hal_init_pins(int numjoints)
{
    INIT_PIN(traj_default_velocity);
    INIT_PIN(traj_max_velocity);
    INIT_PIN(traj_default_acceleration);
    INIT_PIN(traj_max_acceleration);

    INIT_PIN(traj_arc_blend_enable);
    INIT_PIN(traj_arc_blend_fallback_enable);
    INIT_PIN(traj_arc_blend_optimization_depth);
    INIT_PIN(traj_arc_blend_gap_cycles);
    INIT_PIN(traj_arc_blend_ramp_freq);
    INIT_PIN(traj_arc_blend_tangent_kink_ratio);

    for (int idx = 0; idx < numjoints; idx++) {
        INIT_PIN(joint_backlash[idx]);
        INIT_PIN(joint_ferror[idx]);
        INIT_PIN(joint_min_ferror[idx]);
        INIT_PIN(joint_min_limit[idx]);
        INIT_PIN(joint_max_limit[idx]);
        INIT_PIN(joint_max_velocity[idx]);
        INIT_PIN(joint_max_acceleration[idx]);
        INIT_PIN(joint_home[idx]);
        INIT_PIN(joint_home_offset[idx]);
        INIT_PIN(joint_home_sequence[idx]);
    }
    for (int idx = 0; idx < EMCMOT_MAX_AXIS; idx++) {
        INIT_PIN(axis_min_limit[idx]);
        INIT_PIN(axis_max_limit[idx]);
        INIT_PIN(axis_max_velocity[idx]);
        INIT_PIN(axis_max_acceleration[idx]);
    }

    return 0;
} // ini_hal_init_pins()

static void copy_hal_data(const ptr_inihal_data &i, value_inihal_data &j)
{
    int x;
#define FIELD(t,f) j.f = (i.f)?*i.f:0;
#define ARRAY(t,f,n) do { for (x = 0; x < n; x++) j.f[x] = (i.f[x])?*i.f[x]:0; } while (0);
    HAL_FIELDS
#undef FIELD
#undef ARRAY
} // copy_hal_data()

int check_ini_hal_items(int numjoints)
{
    // 全局旧参数快照（上一轮循环保存的 INI 运动参数）；
    value_inihal_data new_inihal_data_mutable;

    // 全局新参数快照（当前循环读取的 INI 运动参数）；
    // 通过 HAL 接口读取 INI 文件中定义的运动参数，保存到 new_inihal_data_mutable 中
    copy_hal_data(*the_inihal_data, new_inihal_data_mutable);

    // 通过引用传递，方便后续代码直接使用 new_inihal_data_mutable 中的参数
    // 只读快照，防止对比过程中被篡改
    const value_inihal_data &new_inihal_data = new_inihal_data_mutable;

    // CHANGED(var)	        对比new_inihal_data.var 和 旧缓存值，返回 1 = 参数发生变化，0 = 无变更
    // NEW(var)	            提取本次快照里新的参数值
    // UPDATE(var)	        把新参数写入全局旧缓存，下一轮循环以此为基准对比
    // SHOW_CHANGE(var)	    debug 模式打印：旧值→新值，用于参数调试追踪

    // 也就是说以下参数是可以中途修改的

    // 全局默认速度
    // 检测 INI [TRAJ] DEFAULT_LINEAR_VELOCITY 是否被修改
    if (CHANGED(traj_default_velocity)) 
    {
        if (debug) 
        {
            // 打印参数变更信息(默认速度)
            SHOW_CHANGE(traj_default_velocity)
        }
        // 更新本地缓存
        UPDATE(traj_default_velocity);
        // 下发新默认速度给motion轨迹层
        // emcTrajSetVelocity()函数用于设置轨迹规划器的默认速度参数，确保运动控制器使用最新的速度配置。
        // 如果设置失败，打印错误信息
        // 这里传参无法理解，为何速度传参0，默认速度传给INI最大速度???将默认速度设置为零，以确保安全性???
        if (0 != emcTrajSetVelocity(0, NEW(traj_default_velocity))) 
        {
            rcs_print("check_ini_hal_items:bad return value from emcTrajSetVelocity\n");
        }
    }

    // 机床最大限制速度
    // 检测 INI [TRAJ] MAX_LINEAR_VELOCITY 是否被修改
    if (CHANGED(traj_max_velocity)) 
    {
        if (debug) 
        {
            SHOW_CHANGE(traj_max_velocity)
        }
        UPDATE(traj_max_velocity);
        // 下发新最大速度给motion轨迹层
        // emcTrajSetMaxVelocity()函数用于设置轨迹规划器的最大速度参数，确保运动控制器使用最新的最大速度配置。
        // 如果设置失败，打印错误信息
        if (0 != emcTrajSetMaxVelocity(NEW(traj_max_velocity))) 
        {
            if (emc_debug & EMC_DEBUG_CONFIG) 
            {
                rcs_print("check_ini_hal_items:bad return value from emcTrajSetMaxVelocity\n");
            }
        }
    }

    // 默认加速度
    // 检测 INI [TRAJ] DEFAULT_LINEAR_ACCELERATION 是否被修改
    if (CHANGED(traj_default_acceleration)) 
    {
        if (debug) 
        {
            SHOW_CHANGE(traj_default_acceleration)
        }
        UPDATE(traj_default_acceleration);
        // 下发新默认加速度给motion轨迹层
        // emcTrajSetAcceleration()函数用于设置轨迹规划器的默认加速度参数，确保运动控制器使用最新的加速度配置。
        // 如果设置失败，打印错误信息
        if (0 != emcTrajSetAcceleration(NEW(traj_default_acceleration))) 
        {
            if (emc_debug & EMC_DEBUG_CONFIG) 
            {
                rcs_print("check_ini_hal_items:bad return value from emcTrajSetAcceleration\n");
            }
        }
    }

    // 最大加速度
    // 检测 INI [TRAJ] MAX_LINEAR_ACCELERATION 是否被修改
    if (CHANGED(traj_max_acceleration)) 
    {
        if (debug) 
        {
            SHOW_CHANGE(traj_max_acceleration)
        }
        UPDATE(traj_max_acceleration);
        // 下发新最大加速度给motion轨迹层
        // emcTrajSetMaxAcceleration()函数用于设置轨迹规划器的最大加速度参数，确保运动控制器使用最新的最大加速度配置。
        // 如果设置失败，打印错误信息
        if (0 != emcTrajSetMaxAcceleration(NEW(traj_max_acceleration))) 
        {
            if (emc_debug & EMC_DEBUG_CONFIG) 
            {
                rcs_print("check_ini_hal_items:bad return value from emcTrajSetMaxAcceleration\n");
            }
        }
    }

    // 检测 INI [TRAJ] ARC_BLEND_* 参数是否被修改
    // ARC_BLEND_ENABLE = 1              	# 圆弧平滑功能使能
    // ARC_BLEND_FALLBACK_ENABLE = 0     	# 圆弧平滑降级模式
    // ARC_BLEND_OPTIMIZATION_DEPTH = 50 	# 圆弧平滑优化深度
    // ARC_BLEND_GAP_CYCLES = 4          	# 圆弧平滑间隙补偿周期
    // ARC_BLEND_RAMP_FREQ = 100.0       	# 圆弧平滑斜坡频率
    // ARC_BLEND_KINK_RATIO = 0.1        	# 圆弧平滑折角判定比例
    // 只要有一个改变就都更新
    if (CHANGED(traj_arc_blend_enable) || CHANGED(traj_arc_blend_fallback_enable) || CHANGED(traj_arc_blend_optimization_depth)
        || CHANGED(traj_arc_blend_gap_cycles) || CHANGED(traj_arc_blend_ramp_freq) || CHANGED(traj_arc_blend_tangent_kink_ratio)) 
    {
        if (debug) 
        {
            SHOW_CHANGE_ARC_BLEND()
        }
        UPDATE(traj_arc_blend_enable);
        UPDATE(traj_arc_blend_fallback_enable);
        UPDATE(traj_arc_blend_optimization_depth);
        UPDATE(traj_arc_blend_gap_cycles);
        UPDATE(traj_arc_blend_ramp_freq);
        UPDATE(traj_arc_blend_tangent_kink_ratio);
        // 下发新圆弧平滑参数给motion轨迹层
        // emcSetupArcBlends()函数用于设置轨迹规划器的圆弧平滑参数，确保运动控制器使用最新的圆弧平滑配置。
        // 如果设置失败，打印错误信息
        // 这里为何会使用old_inihal_data？？？
        // 通过上面的UPDATE（）函数感觉，和上面参数是同等的作用，只是写法不一致，整体还需要再观察???
        if (0 != emcSetupArcBlends(old_inihal_data.traj_arc_blend_enable ,old_inihal_data.traj_arc_blend_fallback_enable ,old_inihal_data.traj_arc_blend_optimization_depth
                                  ,old_inihal_data.traj_arc_blend_gap_cycles ,old_inihal_data.traj_arc_blend_ramp_freq ,old_inihal_data.traj_arc_blend_tangent_kink_ratio )) 
        {
            if (emc_debug & EMC_DEBUG_CONFIG) 
            {
                rcs_print("bad return value from emcSetupArcBlends\n");
            }
            return -1;
        }
    }

    // 检查各个关节的参数是否被修改
    for (int idx = 0; idx < numjoints; idx++) 
    {
        // 丝杠反向间隙补偿量
        // 检测 INI [JOINT] BACKLASH 参数是否被修改
        if (CHANGED_IDX(joint_backlash,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(joint_backlash,idx);
            }
            UPDATE_IDX(joint_backlash,idx);
            if (0 != emcJointSetBacklash(idx,NEW(joint_backlash[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print("check_ini_hal_items:bad return value from emcJointSetBacklash\n");
                }
            }
        }

        // 关节最小位置限制
        // 检测 INI [JOINT] MIN_LIMIT 参数是否被修改
        if (CHANGED_IDX(joint_min_limit,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(joint_min_limit,idx);
            }
            UPDATE_IDX(joint_min_limit,idx);
            if (0 != emcJointSetMinPositionLimit(idx,NEW(joint_min_limit[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcJointSetMinPositionLimit\n");
                }
            }
        }

        // 关节最大位置限制
        // 检测 INI [JOINT] MAX_LIMIT 参数是否被修改
        if (CHANGED_IDX(joint_max_limit,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(joint_max_limit,idx);
            }
            UPDATE_IDX(joint_max_limit,idx);
            if (0 != emcJointSetMaxPositionLimit(idx,NEW(joint_max_limit[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcJointSetMaxPositionLimit\n");
                }
            }
        }

        // 关节最大速度限制
        // 检测 INI [JOINT] MAX_VELOCITY 参数是否被修改
        if (CHANGED_IDX(joint_max_velocity,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(joint_max_velocity,idx);
            }
            UPDATE_IDX(joint_max_velocity,idx);
            if (0 != emcJointSetMaxVelocity(idx, NEW(joint_max_velocity[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcJointSetMaxVelocity\n");
                }
            }
        }

        // 关节最大加速度限制
        // 检测 INI [JOINT] MAX_ACCELERATION 参数是否被修改
        if (CHANGED_IDX(joint_max_acceleration,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(joint_max_acceleration,idx);
            }
            UPDATE_IDX(joint_max_acceleration,idx);
            if (0 != emcJointSetMaxAcceleration(idx, NEW(joint_max_acceleration[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcJointSetMaxAcceleration\n");
                }
            }
        }

        // 关节回零参数
        // 检测 INI [JOINT] HOME 参数是否被修改
        // 检测 INI [JOINT] HOME_OFFSET 参数是否被修改
        // 检测 INI [JOINT] HOME_SEQUENCE 参数是否被修改
        if (   CHANGED_IDX(joint_home,idx)
            || CHANGED_IDX(joint_home_offset,idx)
            || CHANGED_IDX(joint_home_sequence,idx)
           ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(joint_home,idx);
                SHOW_CHANGE_IDX(joint_home_offset,idx);
                SHOW_CHANGE_IDX_INT(joint_home_sequence,idx);
            }
            UPDATE_IDX(joint_home,idx);
            UPDATE_IDX(joint_home_offset,idx);
            UPDATE_IDX(joint_home_sequence,idx);
            if  (0 != emcJointUpdateHomingParams(idx, NEW(joint_home[idx]),
                                                      NEW(joint_home_offset[idx]),
                                                      NEW(joint_home_sequence[idx]))
                ) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcJointUpdateHomingParams\n");
                }
            }
        }

        // 关节反馈误差限制
        // 检测 INI [JOINT] FERROR 参数是否被修改
        if (CHANGED_IDX(joint_ferror,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(joint_ferror,idx);
            }
            UPDATE_IDX(joint_ferror,idx);
            if (0 != emcJointSetFerror(idx,NEW(joint_ferror[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcJointSetFerror\n");
                }
            }
        }

        // 关节最小反馈误差限制
        // 检测 INI [JOINT] MIN_FERROR 参数是否被修改   
        if (CHANGED_IDX(joint_min_ferror,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(joint_min_ferror,idx);
            }
            UPDATE_IDX(joint_min_ferror,idx);
            if (0 != emcJointSetMinFerror(idx,NEW(joint_min_ferror[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcJointSetMinFerror\n");
                }
            }
        }
    } // numjoints

    // 检查各个轴的参数是否被修改
    for (int idx = 0; idx < EMCMOT_MAX_AXIS; idx++) 
    {
        // 轴最小位置限制
        // 检测 INI [AXIS] MIN_LIMIT 参数是否被修改
        if (CHANGED_IDX(axis_min_limit,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(axis_min_limit,idx);
            }
            UPDATE_IDX(axis_min_limit,idx);
            if (0 != emcAxisSetMinPositionLimit(idx,NEW(axis_min_limit[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcAxisSetMinPositionLimit\n");
                }
            }
        }

        // 轴最大位置限制
        // 检测 INI [AXIS] MAX_LIMIT 参数是否被修改
        if (CHANGED_IDX(axis_max_limit,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(axis_max_limit,idx);
            }
            UPDATE_IDX(axis_max_limit,idx);
            if (0 != emcAxisSetMaxPositionLimit(idx,NEW(axis_max_limit[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcAxisSetMaxPositionLimit\n");
                }
            }
        }

        // 轴最大速度限制
        // 检测 INI [AXIS] MAX_VELOCITY 参数是否被
        // ext_offset_a_or_v_ratio : INI [AXIS] OFFSET_AV_RATIO           # A/V五轴联动偏移比例
        if (CHANGED_IDX(axis_max_velocity,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(axis_max_velocity,idx);
            }
            UPDATE_IDX(axis_max_velocity,idx);
            if (0 != emcAxisSetMaxVelocity(idx,
                  (1 - ext_offset_a_or_v_ratio[idx]) * NEW(axis_max_velocity[idx]),
                  (    ext_offset_a_or_v_ratio[idx]) * NEW(axis_max_velocity[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcAxisSetMaxVelocity\n");
                }
            }
        }

        // 轴最大加速度限制
        // 检测 INI [AXIS] MAX_ACCELERATION 参数是否被修改
        // ext_offset_a_or_v_ratio : INI [AXIS] OFFSET_AV_RATIO           # A/V五轴联动偏移比例
        if (CHANGED_IDX(axis_max_acceleration,idx) ) 
        {
            if (debug) 
            {
                SHOW_CHANGE_IDX(axis_max_acceleration,idx);
            }
            UPDATE_IDX(axis_max_acceleration,idx);
            if (0 != emcAxisSetMaxAcceleration(idx,
                  (1 - ext_offset_a_or_v_ratio[idx]) * NEW(axis_max_acceleration[idx]),
                  (    ext_offset_a_or_v_ratio[idx]) * NEW(axis_max_acceleration[idx]))) 
            {
                if (emc_debug & EMC_DEBUG_CONFIG) 
                {
                    rcs_print_error("check_ini_hal_items:bad return from emcAxisSetMaxAcceleration\n");
                }
            }
        }
    } // EMCMOT_MAX_AXIS

    return 0;
} // check_ini_hal_items

// vim: sts=4 sw=4 et
