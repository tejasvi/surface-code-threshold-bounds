import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t108 = true := by
  decide +kernel

theorem tot108 : totK PA10K2 A10K2.t108 = [461295837396, 1432912750626, 1666473999479, 948266517615, 183780684428, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t109 = true := by
  decide +kernel

theorem tot109 : totK PA10K2 A10K2.t109 = [360671191691, 1713908991676, 1979147633547, 558195680979, 32877822373, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t110 = true := by
  decide +kernel

theorem tot110 : totK PA10K2 A10K2.t110 = [0, 710337207927, 2225557661606, 1497020639022, 169754360405, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t111 = true := by
  decide +kernel

theorem tot111 : totK PA10K2 A10K2.t111 = [0, 579763119376, 1882569138837, 1772366067355, 494697705171, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
