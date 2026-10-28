import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7984 = true := by
  decide +kernel

theorem tot7984 : totK PD2M8K2 D2M8K2.t7984 = [0, 0, 200900104152, 469535778021, 251079136294, 24997119171, 0, 0] := by
  decide +kernel

theorem rows7985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7985 = true := by
  decide +kernel

theorem tot7985 : totK PD2M8K2 D2M8K2.t7985 = [0, 0, 200515275816, 501510738266, 204212840271, 10445733409, 0, 0] := by
  decide +kernel

theorem rows7986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7986 = true := by
  decide +kernel

theorem tot7986 : totK PD2M8K2 D2M8K2.t7986 = [0, 0, 166451376215, 448976873692, 226821262013, 13298010109, 0, 0] := by
  decide +kernel

theorem rows7987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7987 = true := by
  decide +kernel

theorem tot7987 : totK PD2M8K2 D2M8K2.t7987 = [0, 0, 78563625841, 337400386463, 381119695253, 76378081257, 1310166938, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
