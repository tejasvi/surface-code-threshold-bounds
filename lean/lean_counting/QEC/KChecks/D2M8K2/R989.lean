import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3956 = true := by
  decide +kernel

theorem tot3956 : totK PD2M8K2 D2M8K2.t3956 = [0, 0, 247517967111, 490395791712, 159383369480, 8470662040, 0, 0] := by
  decide +kernel

theorem rows3957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3957 = true := by
  decide +kernel

theorem tot3957 : totK PD2M8K2 D2M8K2.t3957 = [0, 122003319170, 352957566332, 321775798795, 87164228178, 3521263076, 0, 0] := by
  decide +kernel

theorem rows3958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3958 = true := by
  decide +kernel

theorem tot3958 : totK PD2M8K2 D2M8K2.t3958 = [0, 186109413272, 464936335015, 252061452512, 18495306316, 0, 0, 0] := by
  decide +kernel

theorem rows3959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3959 = true := by
  decide +kernel

theorem tot3959 : totK PD2M8K2 D2M8K2.t3959 = [0, 19036608703, 329260004311, 461587035186, 82214156023, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
