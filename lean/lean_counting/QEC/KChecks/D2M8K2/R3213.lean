import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12852 = true := by
  decide +kernel

theorem tot12852 : totK PD2M8K2 D2M8K2.t12852 = [0, 0, 196353093113, 473112693850, 223373528866, 15844255384, 0, 0] := by
  decide +kernel

theorem rows12853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12853 = true := by
  decide +kernel

theorem tot12853 : totK PD2M8K2 D2M8K2.t12853 = [0, 0, 182858950182, 460476134594, 226354055333, 16702988424, 0, 0] := by
  decide +kernel

theorem rows12854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12854 = true := by
  decide +kernel

theorem tot12854 : totK PD2M8K2 D2M8K2.t12854 = [0, 0, 56013666367, 357397942312, 383954888236, 72585986325, 1095107716, 0] := by
  decide +kernel

theorem rows12855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12855 = true := by
  decide +kernel

theorem tot12855 : totK PD2M8K2 D2M8K2.t12855 = [0, 22713249043, 33897612079, 260894865173, 436297726423, 118498946662, 3882006667, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
