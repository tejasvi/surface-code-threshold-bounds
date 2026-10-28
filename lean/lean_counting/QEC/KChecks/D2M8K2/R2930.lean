import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11720 = true := by
  decide +kernel

theorem tot11720 : totK PD2M8K2 D2M8K2.t11720 = [0, 179679208612, 437083773564, 278421512874, 32993629228, 0, 0, 0] := by
  decide +kernel

theorem rows11721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11721 = true := by
  decide +kernel

theorem tot11721 : totK PD2M8K2 D2M8K2.t11721 = [0, 186683853977, 480537988388, 240333127263, 12423247381, 0, 0, 0] := by
  decide +kernel

theorem rows11722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11722 = true := by
  decide +kernel

theorem tot11722 : totK PD2M8K2 D2M8K2.t11722 = [0, 189659047450, 469419958853, 221638648430, 14715663098, 0, 0, 0] := by
  decide +kernel

theorem rows11723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11723 = true := by
  decide +kernel

theorem tot11723 : totK PD2M8K2 D2M8K2.t11723 = [0, 167467798761, 444000951297, 269985756837, 27817379862, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
