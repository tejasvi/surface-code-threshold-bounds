import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5136 = true := by
  decide +kernel

theorem tot5136 : totK PA10K2 A10K2.t5136 = [0, 113616355882, 723310874730, 1841192393239, 1784591713768, 484225125302, 27250992027, 0, 0, 0] := by
  decide +kernel

theorem rows5137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5137 = true := by
  decide +kernel

theorem tot5137 : totK PA10K2 A10K2.t5137 = [0, 461711995849, 1827633088078, 1949424971166, 481346991955, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5138 = true := by
  decide +kernel

theorem tot5138 : totK PA10K2 A10K2.t5138 = [0, 163282489813, 913701738327, 1820521572626, 1413452852358, 329959078756, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows5139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5139 = true := by
  decide +kernel

theorem tot5139 : totK PA10K2 A10K2.t5139 = [0, 291829445300, 1184487562311, 1876695951671, 1183611233069, 189891953473, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
