import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1428 = true := by
  decide +kernel

theorem tot1428 : totK PA10K2 A10K2.t1428 = [0, 0, 479368079875, 1551890129288, 1462317762409, 578822397452, 498927678708, 265789631412, 28650013862, 0] := by
  decide +kernel

theorem rows1429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1429 = true := by
  decide +kernel

theorem tot1429 : totK PA10K2 A10K2.t1429 = [0, 0, 356956060374, 1615582761809, 2071281775353, 722479151683, 52747279965, 0, 0, 0] := by
  decide +kernel

theorem rows1430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1430 = true := by
  decide +kernel

theorem tot1430 : totK PA10K2 A10K2.t1430 = [0, 0, 0, 464652465079, 1857824427272, 1872836453220, 440310877550, 25371180993, 0, 0] := by
  decide +kernel

theorem rows1431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1431 = true := by
  decide +kernel

theorem tot1431 : totK PA10K2 A10K2.t1431 = [0, 0, 392187269560, 1517173001358, 1942640490681, 801351719226, 109681022248, 5460492893, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
