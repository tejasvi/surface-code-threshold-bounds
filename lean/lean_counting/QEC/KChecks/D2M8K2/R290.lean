import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1160 = true := by
  decide +kernel

theorem tot1160 : totK PD2M8K2 D2M8K2.t1160 = [0, 0, 199095792328, 474304003974, 182761912194, 11947333746, 0, 0] := by
  decide +kernel

theorem rows1161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1161 = true := by
  decide +kernel

theorem tot1161 : totK PD2M8K2 D2M8K2.t1161 = [0, 174800788860, 453070498540, 260470272844, 24627256472, 0, 0, 0] := by
  decide +kernel

theorem rows1162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1162 = true := by
  decide +kernel

theorem tot1162 : totK PD2M8K2 D2M8K2.t1162 = [0, 175589761305, 451660733054, 260534565976, 18594377184, 0, 0, 0] := by
  decide +kernel

theorem rows1163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1163 = true := by
  decide +kernel

theorem tot1163 : totK PD2M8K2 D2M8K2.t1163 = [0, 92932490688, 363990287539, 362575086970, 67024076419, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
