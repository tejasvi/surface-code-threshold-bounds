import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3352 = true := by
  decide +kernel

theorem tot3352 : totK PD2M8K2 D2M8K2.t3352 = [0, 0, 240606263620, 468768175754, 189047692227, 11218555899, 0, 0] := by
  decide +kernel

theorem rows3353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3353 = true := by
  decide +kernel

theorem tot3353 : totK PD2M8K2 D2M8K2.t3353 = [0, 87253921853, 267732073882, 353761209752, 175547911110, 13921987108, 0, 0] := by
  decide +kernel

theorem rows3354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3354 = true := by
  decide +kernel

theorem tot3354 : totK PD2M8K2 D2M8K2.t3354 = [0, 175363559661, 457259308660, 234152776510, 17049611299, 0, 0, 0] := by
  decide +kernel

theorem rows3355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3355 = true := by
  decide +kernel

theorem tot3355 : totK PD2M8K2 D2M8K2.t3355 = [0, 114293998409, 408321520230, 319065369941, 35187301669, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
