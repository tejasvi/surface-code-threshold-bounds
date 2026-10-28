import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1768 = true := by
  decide +kernel

theorem tot1768 : totK PD2M8K2 D2M8K2.t1768 = [0, 0, 84604553198, 337813406110, 362624742918, 90592356288, 4008488258, 0] := by
  decide +kernel

theorem rows1769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1769 = true := by
  decide +kernel

theorem tot1769 : totK PD2M8K2 D2M8K2.t1769 = [0, 0, 176447166952, 468122270903, 249835395024, 13126685180, 0, 0] := by
  decide +kernel

theorem rows1770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1770 = true := by
  decide +kernel

theorem tot1770 : totK PD2M8K2 D2M8K2.t1770 = [0, 0, 145802131707, 438680681509, 285338859731, 24921048683, 0, 0] := by
  decide +kernel

theorem rows1771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1771 = true := by
  decide +kernel

theorem tot1771 : totK PD2M8K2 D2M8K2.t1771 = [0, 0, 0, 253330977226, 474299602464, 141598268857, 5193381917, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
