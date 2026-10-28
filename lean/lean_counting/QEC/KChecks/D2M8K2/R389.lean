import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1556 = true := by
  decide +kernel

theorem tot1556 : totK PD2M8K2 D2M8K2.t1556 = [0, 0, 190639193711, 478026291515, 213754536926, 14704558535, 0, 0] := by
  decide +kernel

theorem rows1557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1557 = true := by
  decide +kernel

theorem tot1557 : totK PD2M8K2 D2M8K2.t1557 = [0, 0, 202529617898, 471946015986, 193233540426, 9653832318, 0, 0] := by
  decide +kernel

theorem rows1558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1558 = true := by
  decide +kernel

theorem tot1558 : totK PD2M8K2 D2M8K2.t1558 = [0, 0, 97940620354, 413706615333, 323476931050, 32536243533, 0, 0] := by
  decide +kernel

theorem rows1559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1559 = true := by
  decide +kernel

theorem tot1559 : totK PD2M8K2 D2M8K2.t1559 = [0, 0, 0, 320001474541, 464676048574, 72854110529, 1206465782, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
