import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1568 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1568 = true := by
  decide +kernel

theorem tot1568 : totK PA10K2 A10K2.t1568 = [0, 0, 0, 160148603592, 884555999063, 1849002224872, 1374005444419, 286090645744, 10545135740, 0] := by
  decide +kernel

theorem rows1569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1569 = true := by
  decide +kernel

theorem tot1569 : totK PA10K2 A10K2.t1569 = [0, 0, 0, 535626000968, 1826528377081, 1743188510686, 451170233647, 30954851499, 0, 0] := by
  decide +kernel

theorem rows1570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1570 = true := by
  decide +kernel

theorem tot1570 : totK PA10K2 A10K2.t1570 = [0, 0, 0, 39814905974, 1175773012166, 2329542363660, 906486344432, 70306993408, 0, 0] := by
  decide +kernel

theorem rows1571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1571 = true := by
  decide +kernel

theorem tot1571 : totK PA10K2 A10K2.t1571 = [0, 0, 0, 530491940114, 1680395544801, 1759613938538, 778467970943, 141370641631, 5528811039, 0] := by
  decide +kernel

end QECKChecks.A10K2
