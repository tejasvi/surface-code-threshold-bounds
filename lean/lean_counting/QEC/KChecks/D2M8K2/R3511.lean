import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14044 = true := by
  decide +kernel

theorem tot14044 : totK PD2M8K2 D2M8K2.t14044 = [0, 0, 248150018028, 512612377077, 137291179662, 1232609433, 0, 0] := by
  decide +kernel

theorem rows14045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14045 = true := by
  decide +kernel

theorem tot14045 : totK PD2M8K2 D2M8K2.t14045 = [0, 0, 180144277397, 466720644596, 224523837433, 9898830947, 0, 0] := by
  decide +kernel

theorem rows14046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14046 = true := by
  decide +kernel

theorem tot14046 : totK PD2M8K2 D2M8K2.t14046 = [0, 0, 238431820052, 479486032966, 147721385063, 9155565991, 0, 0] := by
  decide +kernel

theorem rows14047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14047 = true := by
  decide +kernel

theorem tot14047 : totK PD2M8K2 D2M8K2.t14047 = [0, 0, 231722898842, 457808234343, 217464836999, 21929155944, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
