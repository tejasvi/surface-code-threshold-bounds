import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15968 = true := by
  decide +kernel

theorem tot15968 : totK PD2M8K2 D2M8K2.t15968 = [0, 0, 19692840307, 301477064887, 473954979415, 101971119836, 1268739303, 0] := by
  decide +kernel

theorem rows15969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15969 = true := by
  decide +kernel

theorem tot15969 : totK PD2M8K2 D2M8K2.t15969 = [0, 0, 0, 239028986047, 494100935353, 150752754921, 4918255160, 0] := by
  decide +kernel

theorem rows15970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15970 = true := by
  decide +kernel

theorem tot15970 : totK PD2M8K2 D2M8K2.t15970 = [0, 0, 0, 188297349576, 480594465464, 194345800585, 10086186284, 0] := by
  decide +kernel

theorem rows15971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15971 = true := by
  decide +kernel

theorem tot15971 : totK PD2M8K2 D2M8K2.t15971 = [0, 0, 0, 217055901819, 478878326382, 158921842721, 5293351784, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
