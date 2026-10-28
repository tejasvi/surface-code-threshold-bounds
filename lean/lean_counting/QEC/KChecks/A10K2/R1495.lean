import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5980 = true := by
  decide +kernel

theorem tot5980 : totK PA10K2 A10K2.t5980 = [460697748264, 1603124530067, 1916401154917, 789824415498, 78242053142, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5981 = true := by
  decide +kernel

theorem tot5981 : totK PA10K2 A10K2.t5981 = [289230506492, 1529254479049, 2097622499751, 735677706492, 53383856823, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5982 = true := by
  decide +kernel

theorem tot5982 : totK PA10K2 A10K2.t5982 = [187857973913, 958306811363, 1900313464052, 1368805622803, 248656676753, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5983 = true := by
  decide +kernel

theorem tot5983 : totK PA10K2 A10K2.t5983 = [405291564786, 1740774094191, 2211880265673, 748169442271, 39145761635, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
