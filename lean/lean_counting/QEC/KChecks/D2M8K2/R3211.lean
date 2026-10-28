import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12844 = true := by
  decide +kernel

theorem tot12844 : totK PD2M8K2 D2M8K2.t12844 = [0, 0, 186686565720, 460219945617, 209094770260, 16891742343, 0, 0] := by
  decide +kernel

theorem rows12845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12845 = true := by
  decide +kernel

theorem tot12845 : totK PD2M8K2 D2M8K2.t12845 = [0, 0, 178386979529, 451662080722, 264313990215, 25831956275, 0, 0] := by
  decide +kernel

theorem rows12846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12846 = true := by
  decide +kernel

theorem tot12846 : totK PD2M8K2 D2M8K2.t12846 = [0, 0, 193190840265, 477328437253, 212086315880, 14633607569, 0, 0] := by
  decide +kernel

theorem rows12847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12847 = true := by
  decide +kernel

theorem tot12847 : totK PD2M8K2 D2M8K2.t12847 = [0, 0, 150754534344, 482219208996, 241688516368, 11068810259, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
