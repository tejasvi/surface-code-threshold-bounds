import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t124 = true := by
  decide +kernel

theorem tot124 : totK PA10K2 A10K2.t124 = [0, 458030843142, 1598552717242, 1972329621759, 874650293402, 82653781558, 0, 0, 0, 0] := by
  decide +kernel

theorem rows125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t125 = true := by
  decide +kernel

theorem tot125 : totK PA10K2 A10K2.t125 = [0, 104034905480, 1004602604496, 1961802642430, 1324713842675, 349619169936, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t126 = true := by
  decide +kernel

theorem tot126 : totK PA10K2 A10K2.t126 = [0, 308220282965, 1190342318470, 1819387178696, 1144976370458, 188230699581, 5718040558, 0, 0, 0] := by
  decide +kernel

theorem rows127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t127 = true := by
  decide +kernel

theorem tot127 : totK PA10K2 A10K2.t127 = [0, 428988328460, 1747995031734, 1966626162461, 558021736704, 32877822373, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
