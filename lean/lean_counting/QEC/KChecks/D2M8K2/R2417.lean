import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9668 = true := by
  decide +kernel

theorem tot9668 : totK PD2M8K2 D2M8K2.t9668 = [0, 180558814951, 436557213166, 276638121842, 35253999781, 0, 0, 0] := by
  decide +kernel

theorem rows9669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9669 = true := by
  decide +kernel

theorem tot9669 : totK PD2M8K2 D2M8K2.t9669 = [0, 208170069422, 482247760525, 213626562386, 10688560505, 0, 0, 0] := by
  decide +kernel

theorem rows9670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9670 = true := by
  decide +kernel

theorem tot9670 : totK PD2M8K2 D2M8K2.t9670 = [0, 19382266435, 271979244560, 413093632450, 184369184611, 19355846809, 0, 0] := by
  decide +kernel

theorem rows9671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9671 = true := by
  decide +kernel

theorem tot9671 : totK PD2M8K2 D2M8K2.t9671 = [0, 0, 181644629820, 502138830748, 207375340867, 5335473586, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
