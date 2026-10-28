import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12812 = true := by
  decide +kernel

theorem tot12812 : totK PD2M8K2 D2M8K2.t12812 = [0, 0, 175400641891, 485861722607, 236057600130, 12583874182, 0, 0] := by
  decide +kernel

theorem rows12813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12813 = true := by
  decide +kernel

theorem tot12813 : totK PD2M8K2 D2M8K2.t12813 = [0, 0, 167886362480, 463676642043, 238659377348, 14049597416, 0, 0] := by
  decide +kernel

theorem rows12814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12814 = true := by
  decide +kernel

theorem tot12814 : totK PD2M8K2 D2M8K2.t12814 = [0, 0, 182657694199, 456698844424, 263214607375, 24669294037, 0, 0] := by
  decide +kernel

theorem rows12815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12815 = true := by
  decide +kernel

theorem tot12815 : totK PD2M8K2 D2M8K2.t12815 = [0, 0, 173124426782, 463252779435, 239602810423, 11543300978, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
