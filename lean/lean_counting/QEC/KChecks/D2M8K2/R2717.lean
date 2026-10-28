import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10868 = true := by
  decide +kernel

theorem tot10868 : totK PD2M8K2 D2M8K2.t10868 = [0, 105378643387, 420882978383, 334049591518, 32308746516, 0, 0, 0] := by
  decide +kernel

theorem rows10869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10869 = true := by
  decide +kernel

theorem tot10869 : totK PD2M8K2 D2M8K2.t10869 = [0, 0, 274044334339, 506521865929, 107261318546, 1369150432, 0, 0] := by
  decide +kernel

theorem rows10870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10870 = true := by
  decide +kernel

theorem tot10870 : totK PD2M8K2 D2M8K2.t10870 = [0, 161705976811, 424059934789, 304069718163, 37989616171, 0, 0, 0] := by
  decide +kernel

theorem rows10871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10871 = true := by
  decide +kernel

theorem tot10871 : totK PD2M8K2 D2M8K2.t10871 = [0, 183675373986, 471092763381, 242304254098, 13610570126, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
