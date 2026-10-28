import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3740 = true := by
  decide +kernel

theorem tot3740 : totK PA10K2 A10K2.t3740 = [0, 0, 0, 996227680206, 2409056583735, 1140471098685, 100427183016, 0, 0, 0] := by
  decide +kernel

theorem rows3741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3741 = true := by
  decide +kernel

theorem tot3741 : totK PA10K2 A10K2.t3741 = [0, 0, 0, 496013992925, 1814531271144, 1731955277563, 456274295146, 31193230065, 0, 0] := by
  decide +kernel

theorem rows3742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3742 = true := by
  decide +kernel

theorem tot3742 : totK PA10K2 A10K2.t3742 = [0, 0, 0, 599914939471, 2047949325237, 1697424251497, 294436829060, 6354603908, 0, 0] := by
  decide +kernel

theorem rows3743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3743 = true := by
  decide +kernel

theorem tot3743 : totK PA10K2 A10K2.t3743 = [0, 0, 0, 554091089285, 1868963401142, 1781960655080, 470493697602, 31690783744, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
