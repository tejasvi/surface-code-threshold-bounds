import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4740 = true := by
  decide +kernel

theorem tot4740 : totK PA10K2 A10K2.t4740 = [0, 0, 627091868329, 2030080087482, 1716078522600, 408993665170, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows4741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4741 = true := by
  decide +kernel

theorem tot4741 : totK PA10K2 A10K2.t4741 = [0, 299996936876, 1139595614588, 1768186326325, 1279299441535, 228635617466, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows4742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4742 = true := by
  decide +kernel

theorem tot4742 : totK PA10K2 A10K2.t4742 = [0, 470692171148, 1868929675413, 1938804999712, 499358426425, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4743 = true := by
  decide +kernel

theorem tot4743 : totK PA10K2 A10K2.t4743 = [0, 0, 807314867616, 2346166008660, 1431283665113, 148425478084, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
