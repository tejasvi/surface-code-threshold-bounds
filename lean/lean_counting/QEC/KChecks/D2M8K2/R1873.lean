import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7492 = true := by
  decide +kernel

theorem tot7492 : totK PD2M8K2 D2M8K2.t7492 = [0, 169300515430, 456242230810, 258866702472, 15821605505, 0, 0, 0] := by
  decide +kernel

theorem rows7493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7493 = true := by
  decide +kernel

theorem tot7493 : totK PD2M8K2 D2M8K2.t7493 = [0, 0, 243100798022, 502656251503, 146164860567, 2304167554, 0, 0] := by
  decide +kernel

theorem rows7494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7494 = true := by
  decide +kernel

theorem tot7494 : totK PD2M8K2 D2M8K2.t7494 = [0, 0, 168182178989, 480085381777, 214379920188, 8490945260, 0, 0] := by
  decide +kernel

theorem rows7495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7495 = true := by
  decide +kernel

theorem tot7495 : totK PD2M8K2 D2M8K2.t7495 = [0, 0, 197281319475, 466944055136, 210067412153, 16367851922, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
