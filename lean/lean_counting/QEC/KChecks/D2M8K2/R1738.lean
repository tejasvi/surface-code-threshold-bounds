import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6952 = true := by
  decide +kernel

theorem tot6952 : totK PD2M8K2 D2M8K2.t6952 = [0, 211786255742, 473406898291, 185261530896, 7941657394, 0, 0, 0] := by
  decide +kernel

theorem rows6953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6953 = true := by
  decide +kernel

theorem tot6953 : totK PD2M8K2 D2M8K2.t6953 = [0, 0, 286317697302, 495795168164, 102204041446, 1369150432, 0, 0] := by
  decide +kernel

theorem rows6954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6954 = true := by
  decide +kernel

theorem tot6954 : totK PD2M8K2 D2M8K2.t6954 = [0, 92986855429, 382092249996, 388322811316, 49638201523, 0, 0, 0] := by
  decide +kernel

theorem rows6955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6955 = true := by
  decide +kernel

theorem tot6955 : totK PD2M8K2 D2M8K2.t6955 = [0, 157883578780, 446324905578, 283550596548, 24033389359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
