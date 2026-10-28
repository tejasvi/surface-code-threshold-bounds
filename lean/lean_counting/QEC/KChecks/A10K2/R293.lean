import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1172 = true := by
  decide +kernel

theorem tot1172 : totK PA10K2 A10K2.t1172 = [0, 0, 703816319330, 2073169429162, 1685704871746, 397377559848, 25351274858, 0, 0, 0] := by
  decide +kernel

theorem rows1173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1173 = true := by
  decide +kernel

theorem tot1173 : totK PA10K2 A10K2.t1173 = [0, 327932994659, 1297562295403, 1999729906176, 1219921825818, 197084726890, 5459593153, 0, 0, 0] := by
  decide +kernel

theorem rows1174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1174 = true := by
  decide +kernel

theorem tot1174 : totK PA10K2 A10K2.t1174 = [0, 149549839681, 1119845471284, 2230374330287, 1410688727916, 227196534959, 8047840951, 0, 0, 0] := by
  decide +kernel

theorem rows1175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1175 = true := by
  decide +kernel

theorem tot1175 : totK PA10K2 A10K2.t1175 = [0, 512637402434, 1816664556758, 1920445364260, 698358381593, 66069361460, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
