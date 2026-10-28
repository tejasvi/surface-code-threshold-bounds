import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t544 = true := by
  decide +kernel

theorem tot544 : totK PA10K2 A10K2.t544 = [157101129727, 1110941593581, 2106541340958, 1327798854225, 261510434082, 6962742351, 0, 0, 0, 0] := by
  decide +kernel

theorem rows545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t545 = true := by
  decide +kernel

theorem tot545 : totK PA10K2 A10K2.t545 = [0, 454575959798, 1861972100285, 1884487430623, 456427790797, 26479096260, 0, 0, 0, 0] := by
  decide +kernel

theorem rows546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t546 = true := by
  decide +kernel

theorem tot546 : totK PA10K2 A10K2.t546 = [0, 188521259194, 1029778611201, 2022438135159, 1341122463626, 275325662550, 20331139758, 0, 0, 0] := by
  decide +kernel

theorem rows547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t547 = true := by
  decide +kernel

theorem tot547 : totK PA10K2 A10K2.t547 = [0, 202308092638, 1001027138705, 1843131220585, 1390853577356, 296248272163, 10751746851, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
