import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5036 = true := by
  decide +kernel

theorem tot5036 : totK PA10K2 A10K2.t5036 = [0, 526179114281, 1901765700490, 1892837896383, 428702987049, 11765040145, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5037 = true := by
  decide +kernel

theorem tot5037 : totK PA10K2 A10K2.t5037 = [0, 0, 626761192682, 2040601695315, 1708124040934, 394579472451, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows5038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5038 = true := by
  decide +kernel

theorem tot5038 : totK PA10K2 A10K2.t5038 = [0, 292130592925, 1196408931926, 1845803839380, 1176860774004, 190336912606, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5039 = true := by
  decide +kernel

theorem tot5039 : totK PA10K2 A10K2.t5039 = [0, 453828566602, 1675854680165, 1870144657528, 628220323002, 51782903379, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
