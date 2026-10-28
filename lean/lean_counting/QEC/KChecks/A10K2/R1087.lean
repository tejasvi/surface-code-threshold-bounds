import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4348 = true := by
  decide +kernel

theorem tot4348 : totK PA10K2 A10K2.t4348 = [0, 0, 0, 469631274813, 1794606886052, 1900194355239, 506221389200, 31987755669, 0, 0] := by
  decide +kernel

theorem rows4349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4349 = true := by
  decide +kernel

theorem tot4349 : totK PA10K2 A10K2.t4349 = [0, 0, 0, 589804994150, 2020968289461, 1750443438488, 373772903014, 12918102615, 0, 0] := by
  decide +kernel

theorem rows4350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4350 = true := by
  decide +kernel

theorem tot4350 : totK PA10K2 A10K2.t4350 = [0, 0, 0, 508407227338, 1831588431946, 1816403627882, 433090629466, 30595569240, 0, 0] := by
  decide +kernel

theorem rows4351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4351 = true := by
  decide +kernel

theorem tot4351 : totK PA10K2 A10K2.t4351 = [0, 0, 0, 465795714142, 1825636087645, 1768341715414, 384108067006, 25958654434, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
