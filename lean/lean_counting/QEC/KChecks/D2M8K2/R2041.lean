import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8164 = true := by
  decide +kernel

theorem tot8164 : totK PD2M8K2 D2M8K2.t8164 = [0, 104315706752, 427532659507, 347956989175, 30339501789, 0, 0, 0] := by
  decide +kernel

theorem rows8165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8165 = true := by
  decide +kernel

theorem tot8165 : totK PD2M8K2 D2M8K2.t8165 = [0, 0, 211741048175, 489745988173, 178326738765, 4965269624, 0, 0] := by
  decide +kernel

theorem rows8166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8166 = true := by
  decide +kernel

theorem tot8166 : totK PD2M8K2 D2M8K2.t8166 = [0, 0, 186923614192, 465783233309, 216998183739, 17076867616, 0, 0] := by
  decide +kernel

theorem rows8167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8167 = true := by
  decide +kernel

theorem tot8167 : totK PD2M8K2 D2M8K2.t8167 = [0, 0, 188338233481, 499717943587, 193969723032, 3705122438, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
