import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4588 = true := by
  decide +kernel

theorem tot4588 : totK PA10K2 A10K2.t4588 = [0, 0, 551924593002, 1853005330080, 1775497217227, 463492548166, 31193230065, 0, 0, 0] := by
  decide +kernel

theorem rows4589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4589 = true := by
  decide +kernel

theorem tot4589 : totK PA10K2 A10K2.t4589 = [0, 0, 565343474017, 1885460306380, 1792505689073, 471346917457, 31690778550, 0, 0, 0] := by
  decide +kernel

theorem rows4590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4590 = true := by
  decide +kernel

theorem tot4590 : totK PA10K2 A10K2.t4590 = [0, 0, 541382630248, 1911910519088, 1780606161027, 392134600624, 25589850627, 0, 0, 0] := by
  decide +kernel

theorem rows4591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4591 = true := by
  decide +kernel

theorem tot4591 : totK PA10K2 A10K2.t4591 = [0, 0, 571262723167, 1874584198872, 1688780007910, 434896777261, 30874154442, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
