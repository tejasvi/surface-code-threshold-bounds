import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t512 = true := by
  decide +kernel

theorem tot512 : totK PA10K2 A10K2.t512 = [0, 282589431047, 1505031643967, 2158165382471, 799484256895, 49880460014, 0, 0, 0, 0] := by
  decide +kernel

theorem rows513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t513 = true := by
  decide +kernel

theorem tot513 : totK PA10K2 A10K2.t513 = [0, 302796269763, 1261153120480, 1904327616565, 1071125384849, 174379415110, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t514 = true := by
  decide +kernel

theorem tot514 : totK PA10K2 A10K2.t514 = [0, 467131606573, 1791975489861, 2025373829704, 584169636772, 19117496088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t515 = true := by
  decide +kernel

theorem tot515 : totK PA10K2 A10K2.t515 = [0, 0, 579035095310, 1969334043521, 1765754962553, 416785110678, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
