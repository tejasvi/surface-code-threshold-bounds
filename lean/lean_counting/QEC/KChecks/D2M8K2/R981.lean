import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3924 = true := by
  decide +kernel

theorem tot3924 : totK PD2M8K2 D2M8K2.t3924 = [0, 0, 227656439009, 486196015509, 163000210893, 9404247146, 0, 0] := by
  decide +kernel

theorem rows3925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3925 = true := by
  decide +kernel

theorem tot3925 : totK PD2M8K2 D2M8K2.t3925 = [0, 152451502468, 414015156155, 280963103484, 57749566595, 2481160468, 0, 0] := by
  decide +kernel

theorem rows3926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3926 = true := by
  decide +kernel

theorem tot3926 : totK PD2M8K2 D2M8K2.t3926 = [0, 174557790337, 455889206247, 256635736883, 16899899759, 0, 0, 0] := by
  decide +kernel

theorem rows3927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3927 = true := by
  decide +kernel

theorem tot3927 : totK PD2M8K2 D2M8K2.t3927 = [0, 0, 304332886701, 496294426629, 87104430366, 1062926506, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
