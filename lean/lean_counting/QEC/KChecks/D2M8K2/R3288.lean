import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13152 = true := by
  decide +kernel

theorem tot13152 : totK PD2M8K2 D2M8K2.t13152 = [0, 0, 170450294341, 388610554182, 238001453964, 69807248239, 3667207281, 0] := by
  decide +kernel

theorem rows13153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13153 = true := by
  decide +kernel

theorem tot13153 : totK PD2M8K2 D2M8K2.t13153 = [0, 0, 170210732491, 444039689268, 267138329165, 17869629627, 0, 0] := by
  decide +kernel

theorem rows13154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13154 = true := by
  decide +kernel

theorem tot13154 : totK PD2M8K2 D2M8K2.t13154 = [0, 122548150330, 334760686240, 291540384946, 138795614947, 11723623870, 0, 0] := by
  decide +kernel

theorem rows13155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13155 = true := by
  decide +kernel

theorem tot13155 : totK PD2M8K2 D2M8K2.t13155 = [0, 185620455532, 451357493745, 229940574946, 17115888737, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
