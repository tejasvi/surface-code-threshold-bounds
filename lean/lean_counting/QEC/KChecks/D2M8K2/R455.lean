import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1820 = true := by
  decide +kernel

theorem tot1820 : totK PD2M8K2 D2M8K2.t1820 = [0, 0, 331525397869, 508613077560, 81835571463, 0, 0, 0] := by
  decide +kernel

theorem rows1821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1821 = true := by
  decide +kernel

theorem tot1821 : totK PD2M8K2 D2M8K2.t1821 = [0, 157483264256, 371709640173, 280967755184, 88511863536, 3880716147, 0, 0] := by
  decide +kernel

theorem rows1822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1822 = true := by
  decide +kernel

theorem tot1822 : totK PD2M8K2 D2M8K2.t1822 = [0, 173417358554, 452074047937, 259852232361, 19808608805, 0, 0, 0] := by
  decide +kernel

theorem rows1823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1823 = true := by
  decide +kernel

theorem tot1823 : totK PD2M8K2 D2M8K2.t1823 = [0, 75019876041, 337137400312, 395907361987, 91728116257, 1267860612, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
