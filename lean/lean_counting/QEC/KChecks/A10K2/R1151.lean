import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4604 = true := by
  decide +kernel

theorem tot4604 : totK PA10K2 A10K2.t4604 = [0, 292336804476, 1266910070473, 1907381773679, 1147398859978, 194056191006, 5517381808, 0, 0, 0] := by
  decide +kernel

theorem rows4605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4605 = true := by
  decide +kernel

theorem tot4605 : totK PA10K2 A10K2.t4605 = [0, 268323897024, 1444408765465, 2183046545767, 831064317918, 46129175324, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4606 = true := by
  decide +kernel

theorem tot4606 : totK PA10K2 A10K2.t4606 = [0, 418179822483, 1446461569775, 1832933916985, 986578099527, 174546124065, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows4607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4607 = true := by
  decide +kernel

theorem tot4607 : totK PA10K2 A10K2.t4607 = [0, 385288804524, 1701911130073, 2188681754833, 730136694561, 38670148117, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
