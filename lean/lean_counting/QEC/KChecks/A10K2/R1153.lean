import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4612 = true := by
  decide +kernel

theorem tot4612 : totK PA10K2 A10K2.t4612 = [0, 563568958889, 1967633878088, 1880042783759, 487295271322, 31677228370, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4613 = true := by
  decide +kernel

theorem tot4613 : totK PA10K2 A10K2.t4613 = [538725919627, 1847332730153, 1876438066301, 631519189905, 71900000892, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4614 = true := by
  decide +kernel

theorem tot4614 : totK PA10K2 A10K2.t4614 = [329616625233, 1526984137911, 2140803500188, 903173450568, 75149764344, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4615 = true := by
  decide +kernel

theorem tot4615 : totK PA10K2 A10K2.t4615 = [0, 563764530763, 2038560132747, 1987386884381, 465717198556, 13816090359, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
