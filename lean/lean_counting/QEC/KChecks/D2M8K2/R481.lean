import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1924 = true := by
  decide +kernel

theorem tot1924 : totK PD2M8K2 D2M8K2.t1924 = [0, 0, 276583675152, 504547305712, 121255398929, 1268739303, 0, 0] := by
  decide +kernel

theorem rows1925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1925 = true := by
  decide +kernel

theorem tot1925 : totK PD2M8K2 D2M8K2.t1925 = [0, 0, 194918383006, 490531410644, 188276150064, 7442000727, 0, 0] := by
  decide +kernel

theorem rows1926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1926 = true := by
  decide +kernel

theorem tot1926 : totK PD2M8K2 D2M8K2.t1926 = [0, 0, 175717010161, 462920690900, 234762190187, 15859045170, 0, 0] := by
  decide +kernel

theorem rows1927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1927 = true := by
  decide +kernel

theorem tot1927 : totK PD2M8K2 D2M8K2.t1927 = [0, 0, 182149681515, 475506774456, 208644108274, 7913321096, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
