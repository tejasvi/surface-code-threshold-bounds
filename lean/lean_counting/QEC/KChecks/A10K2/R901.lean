import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3604 = true := by
  decide +kernel

theorem tot3604 : totK PA10K2 A10K2.t3604 = [0, 0, 0, 126240364679, 1403940365075, 2215897926875, 760020381783, 57703080492, 0, 0] := by
  decide +kernel

theorem rows3605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3605 = true := by
  decide +kernel

theorem tot3605 : totK PA10K2 A10K2.t3605 = [0, 329682097654, 1182155827690, 1273466331906, 501409497141, 663261611574, 625299479746, 134586829158, 5676195732, 0] := by
  decide +kernel

theorem rows3606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3606 = true := by
  decide +kernel

theorem tot3606 : totK PA10K2 A10K2.t3606 = [0, 518434751736, 1927944576036, 1947457009671, 496927262662, 13227942247, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3607 = true := by
  decide +kernel

theorem tot3607 : totK PA10K2 A10K2.t3607 = [0, 0, 626599893289, 2018695365329, 1737195802079, 412826910099, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
