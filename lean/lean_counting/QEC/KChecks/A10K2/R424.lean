import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1696 = true := by
  decide +kernel

theorem tot1696 : totK PA10K2 A10K2.t1696 = [0, 0, 293909612562, 1538395020827, 2096519506190, 702153977196, 40463368338, 0, 0, 0] := by
  decide +kernel

theorem rows1697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1697 = true := by
  decide +kernel

theorem tot1697 : totK PA10K2 A10K2.t1697 = [0, 0, 106707522138, 578216830722, 1696880157128, 1668343391782, 441155992452, 31003444686, 0, 0] := by
  decide +kernel

theorem rows1698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1698 = true := by
  decide +kernel

theorem tot1698 : totK PA10K2 A10K2.t1698 = [0, 0, 430145912226, 1714287239604, 1922671665268, 558207615485, 46060145381, 0, 0, 0] := by
  decide +kernel

theorem rows1699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1699 = true := by
  decide +kernel

theorem tot1699 : totK PA10K2 A10K2.t1699 = [0, 0, 309832231131, 1555502524339, 2088445504921, 727228890294, 44985272281, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
