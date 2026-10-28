import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7144 = true := by
  decide +kernel

theorem tot7144 : totK PA10K2 A10K2.t7144 = [0, 0, 0, 386323148565, 1583824846276, 1807802855522, 525010848963, 37079283060, 0, 0] := by
  decide +kernel

theorem rows7145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7145 = true := by
  decide +kernel

theorem tot7145 : totK PA10K2 A10K2.t7145 = [0, 0, 0, 113147589240, 866903650226, 1998881562725, 1229347748671, 190652441267, 5528811039, 0] := by
  decide +kernel

theorem rows7146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7146 = true := by
  decide +kernel

theorem tot7146 : totK PA10K2 A10K2.t7146 = [0, 0, 0, 669469346759, 2159930755710, 1880878956799, 353369234119, 14900762211, 0, 0] := by
  decide +kernel

theorem rows7147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7147 = true := by
  decide +kernel

theorem tot7147 : totK PA10K2 A10K2.t7147 = [0, 0, 470372318891, 1518662489217, 1628556570031, 926658939864, 317633000566, 29010686974, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
