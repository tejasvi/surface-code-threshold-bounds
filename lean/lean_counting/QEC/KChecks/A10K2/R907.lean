import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3628 = true := by
  decide +kernel

theorem tot3628 : totK PA10K2 A10K2.t3628 = [0, 0, 503479624534, 1860757170173, 1769271461016, 423334290976, 26601763172, 0, 0, 0] := by
  decide +kernel

theorem rows3629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3629 = true := by
  decide +kernel

theorem tot3629 : totK PA10K2 A10K2.t3629 = [0, 0, 581321856993, 1962750395731, 1821808952195, 404152633673, 11740596405, 0, 0, 0] := by
  decide +kernel

theorem rows3630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3630 = true := by
  decide +kernel

theorem tot3630 : totK PA10K2 A10K2.t3630 = [0, 0, 483444569140, 1856144909978, 1991707567557, 521580250980, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows3631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3631 = true := by
  decide +kernel

theorem tot3631 : totK PA10K2 A10K2.t3631 = [0, 0, 504218616469, 1758901841797, 1846249727871, 522118198149, 31607162994, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
