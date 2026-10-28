import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4596 = true := by
  decide +kernel

theorem tot4596 : totK PA10K2 A10K2.t4596 = [354111422834, 1491889216970, 2020332981645, 971926525185, 146392591255, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4597 = true := by
  decide +kernel

theorem tot4597 : totK PA10K2 A10K2.t4597 = [207342027836, 1369069693199, 2189861638491, 933381589886, 80263277063, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4598 = true := by
  decide +kernel

theorem tot4598 : totK PA10K2 A10K2.t4598 = [487223217921, 1613046797531, 1841842727905, 879164793523, 181948244845, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4599 = true := by
  decide +kernel

theorem tot4599 : totK PA10K2 A10K2.t4599 = [316779408161, 1477984699010, 2176796275927, 978753576956, 91581292198, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
