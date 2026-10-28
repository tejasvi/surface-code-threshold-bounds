import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6004 = true := by
  decide +kernel

theorem tot6004 : totK PD2M8K2 D2M8K2.t6004 = [0, 189400078614, 479978709838, 222379306465, 12340935526, 0, 0, 0] := by
  decide +kernel

theorem rows6005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6005 = true := by
  decide +kernel

theorem tot6005 : totK PD2M8K2 D2M8K2.t6005 = [0, 15861998191, 306750110027, 471781076032, 100204268506, 1164319620, 0, 0] := by
  decide +kernel

theorem rows6006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6006 = true := by
  decide +kernel

theorem tot6006 : totK PD2M8K2 D2M8K2.t6006 = [0, 0, 196522426225, 477586988866, 192080262670, 11885407614, 0, 0] := by
  decide +kernel

theorem rows6007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6007 = true := by
  decide +kernel

theorem tot6007 : totK PD2M8K2 D2M8K2.t6007 = [0, 165819165509, 441696645490, 268814913938, 30257739842, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
