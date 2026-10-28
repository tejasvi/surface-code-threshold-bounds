import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1680 = true := by
  decide +kernel

theorem tot1680 : totK PD2M8K2 D2M8K2.t1680 = [0, 0, 172453097909, 436305006018, 262575343859, 23361464901, 0, 0] := by
  decide +kernel

theorem rows1681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1681 = true := by
  decide +kernel

theorem tot1681 : totK PD2M8K2 D2M8K2.t1681 = [0, 0, 184365389885, 466153062487, 216735431145, 12373752831, 0, 0] := by
  decide +kernel

theorem rows1682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1682 = true := by
  decide +kernel

theorem tot1682 : totK PD2M8K2 D2M8K2.t1682 = [0, 0, 55669940329, 333815655277, 408282933230, 79047257267, 1164319620, 0] := by
  decide +kernel

theorem rows1683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1683 = true := by
  decide +kernel

theorem tot1683 : totK PD2M8K2 D2M8K2.t1683 = [0, 0, 0, 197148415178, 462226167151, 169494623287, 11727338389, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
