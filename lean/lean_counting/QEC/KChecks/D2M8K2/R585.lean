import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2340 = true := by
  decide +kernel

theorem tot2340 : totK PD2M8K2 D2M8K2.t2340 = [0, 175638020212, 444898320122, 263393754251, 20219658679, 0, 0, 0] := by
  decide +kernel

theorem rows2341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2341 = true := by
  decide +kernel

theorem tot2341 : totK PD2M8K2 D2M8K2.t2341 = [0, 89076128973, 370943556003, 365267578529, 66714070202, 1164319620, 0, 0] := by
  decide +kernel

theorem rows2342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2342 = true := by
  decide +kernel

theorem tot2342 : totK PD2M8K2 D2M8K2.t2342 = [0, 0, 245272269113, 487106144885, 157032260207, 8423393484, 0, 0] := by
  decide +kernel

theorem rows2343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2343 = true := by
  decide +kernel

theorem tot2343 : totK PD2M8K2 D2M8K2.t2343 = [0, 119372288294, 350815241834, 331716086330, 86051246337, 3462014130, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
