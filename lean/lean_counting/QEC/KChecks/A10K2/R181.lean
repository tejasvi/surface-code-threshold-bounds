import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t724 = true := by
  decide +kernel

theorem tot724 : totK PA10K2 A10K2.t724 = [319295482399, 1106832952836, 1146272005506, 340459023607, 151860354184, 707423249552, 737143629413, 187952782646, 6354482628, 0] := by
  decide +kernel

theorem rows725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t725 = true := by
  decide +kernel

theorem tot725 : totK PA10K2 A10K2.t725 = [540085626012, 1903460170015, 1934968268545, 503672840061, 18696211658, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t726 = true := by
  decide +kernel

theorem tot726 : totK PA10K2 A10K2.t726 = [0, 678516228980, 2014926999520, 1655288749704, 397995866641, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t727 = true := by
  decide +kernel

theorem tot727 : totK PA10K2 A10K2.t727 = [291924723771, 1175865715920, 1888734679060, 1259264133597, 214682274080, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
