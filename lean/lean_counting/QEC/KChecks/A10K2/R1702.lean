import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6808 = true := by
  decide +kernel

theorem tot6808 : totK PA10K2 A10K2.t6808 = [0, 15795371065, 491597127260, 1750212547338, 1805399679508, 501357616061, 31082886609, 0, 0, 0] := by
  decide +kernel

theorem rows6809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6809 = true := by
  decide +kernel

theorem tot6809 : totK PA10K2 A10K2.t6809 = [0, 427950813453, 1718957562982, 1957488929326, 620380844465, 48302371891, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6810 = true := by
  decide +kernel

theorem tot6810 : totK PA10K2 A10K2.t6810 = [0, 331207170276, 1363565381134, 2011648054316, 1042282402950, 157986454226, 6121173289, 0, 0, 0] := by
  decide +kernel

theorem rows6811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6811 = true := by
  decide +kernel

theorem tot6811 : totK PA10K2 A10K2.t6811 = [0, 501031323376, 1904632386989, 2002836956994, 567092823476, 31625987855, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
