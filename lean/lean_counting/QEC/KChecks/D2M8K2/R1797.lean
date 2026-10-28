import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7188 = true := by
  decide +kernel

theorem tot7188 : totK PD2M8K2 D2M8K2.t7188 = [0, 166649519338, 438636968986, 263867526982, 23205715982, 0, 0, 0] := by
  decide +kernel

theorem rows7189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7189 = true := by
  decide +kernel

theorem tot7189 : totK PD2M8K2 D2M8K2.t7189 = [0, 63596481800, 329434101396, 417463296082, 89986765492, 1198073392, 0, 0] := by
  decide +kernel

theorem rows7190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7190 = true := by
  decide +kernel

theorem tot7190 : totK PD2M8K2 D2M8K2.t7190 = [0, 18567060971, 264784398487, 475209423069, 133069691444, 4257574148, 0, 0] := by
  decide +kernel

theorem rows7191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7191 = true := by
  decide +kernel

theorem tot7191 : totK PD2M8K2 D2M8K2.t7191 = [0, 189542363181, 467055536129, 243775552823, 21062381785, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
