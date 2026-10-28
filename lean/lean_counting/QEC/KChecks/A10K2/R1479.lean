import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5916 = true := by
  decide +kernel

theorem tot5916 : totK PA10K2 A10K2.t5916 = [348908477125, 1192584003896, 1588450001546, 1268935861449, 535378423229, 50300197778, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5917 = true := by
  decide +kernel

theorem tot5917 : totK PA10K2 A10K2.t5917 = [432541415594, 1768140653369, 1991945387238, 654316874738, 49566425333, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5918 = true := by
  decide +kernel

theorem tot5918 : totK PA10K2 A10K2.t5918 = [0, 517389616574, 1938797946139, 1792002218282, 416006335286, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5919 = true := by
  decide +kernel

theorem tot5919 : totK PA10K2 A10K2.t5919 = [251956656316, 1334650394845, 1998402449510, 1017703273252, 166441446197, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
