import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7572 = true := by
  decide +kernel

theorem tot7572 : totK PA10K2 A10K2.t7572 = [0, 0, 0, 705572462520, 2087079236348, 1598368563108, 376582195821, 25565504801, 0, 0] := by
  decide +kernel

theorem rows7573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7573 = true := by
  decide +kernel

theorem tot7573 : totK PA10K2 A10K2.t7573 = [0, 0, 288340708618, 1254272655066, 1873909143238, 1135239997664, 194887479854, 5517381808, 0, 0] := by
  decide +kernel

theorem rows7574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7574 = true := by
  decide +kernel

theorem tot7574 : totK PA10K2 A10K2.t7574 = [0, 0, 233627348966, 1358738859751, 2147405204068, 870085726970, 66746940613, 0, 0, 0] := by
  decide +kernel

theorem rows7575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7575 = true := by
  decide +kernel

theorem tot7575 : totK PA10K2 A10K2.t7575 = [0, 0, 389033160192, 1432837322622, 1864915255031, 961322995093, 162757325801, 6121173289, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
