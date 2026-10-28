import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12736 = true := by
  decide +kernel

theorem tot12736 : totK PD2M8K2 D2M8K2.t12736 = [0, 0, 182735830479, 444708100389, 277565897659, 33269352914, 0, 0] := by
  decide +kernel

theorem rows12737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12737 = true := by
  decide +kernel

theorem tot12737 : totK PD2M8K2 D2M8K2.t12737 = [0, 0, 176467387261, 482540998535, 242875038934, 9364425973, 0, 0] := by
  decide +kernel

theorem rows12738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12738 = true := by
  decide +kernel

theorem tot12738 : totK PD2M8K2 D2M8K2.t12738 = [0, 0, 88693638382, 321460477828, 357288562094, 136125426904, 15856679686, 0] := by
  decide +kernel

theorem rows12739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12739 = true := by
  decide +kernel

theorem tot12739 : totK PD2M8K2 D2M8K2.t12739 = [0, 0, 0, 187586316893, 466400127629, 218698603050, 13187769311, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
