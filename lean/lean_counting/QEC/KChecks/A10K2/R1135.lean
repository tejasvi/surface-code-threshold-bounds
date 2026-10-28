import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4540 = true := by
  decide +kernel

theorem tot4540 : totK PA10K2 A10K2.t4540 = [0, 627091868329, 2025575951318, 1716650666686, 409543331805, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4541 = true := by
  decide +kernel

theorem tot4541 : totK PA10K2 A10K2.t4541 = [299996936876, 1139595614588, 1781058889211, 1282712851559, 229624171397, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4542 = true := by
  decide +kernel

theorem tot4542 : totK PA10K2 A10K2.t4542 = [470692171148, 1854874033778, 1951460625569, 499358426425, 26521581199, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4543 = true := by
  decide +kernel

theorem tot4543 : totK PA10K2 A10K2.t4543 = [0, 807314867616, 2359808320457, 1430709064225, 148856532434, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
