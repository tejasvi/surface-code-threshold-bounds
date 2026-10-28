import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1240 = true := by
  decide +kernel

theorem tot1240 : totK PD2M8K2 D2M8K2.t1240 = [0, 195231917801, 464948697144, 245041241515, 23024857527, 0, 0, 0] := by
  decide +kernel

theorem rows1241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1241 = true := by
  decide +kernel

theorem tot1241 : totK PD2M8K2 D2M8K2.t1241 = [0, 178990277107, 471168404399, 239581774017, 13115924424, 0, 0, 0] := by
  decide +kernel

theorem rows1242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1242 = true := by
  decide +kernel

theorem tot1242 : totK PD2M8K2 D2M8K2.t1242 = [0, 0, 324303710422, 480362095391, 92110376154, 1238673482, 0, 0] := by
  decide +kernel

theorem rows1243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1243 = true := by
  decide +kernel

theorem tot1243 : totK PD2M8K2 D2M8K2.t1243 = [18872545859, 24649648434, 174587218827, 457765893860, 191583164042, 8063697217, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
