import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4728 = true := by
  decide +kernel

theorem tot4728 : totK PA10K2 A10K2.t4728 = [0, 0, 0, 559417836928, 2052489505892, 1938001153270, 441266411786, 12926121504, 0, 0] := by
  decide +kernel

theorem rows4729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4729 = true := by
  decide +kernel

theorem tot4729 : totK PA10K2 A10K2.t4729 = [0, 571579400012, 1797635149501, 1566922374131, 458724034930, 261281045892, 173654520793, 28664533810, 0, 0] := by
  decide +kernel

theorem rows4730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4730 = true := by
  decide +kernel

theorem tot4730 : totK PA10K2 A10K2.t4730 = [0, 188386102229, 1270462001830, 2273890643980, 1103758154373, 100911626157, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4731 = true := by
  decide +kernel

theorem tot4731 : totK PA10K2 A10K2.t4731 = [0, 110625755653, 680788950270, 1751623079493, 1710124357663, 465049642324, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
