import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1784 = true := by
  decide +kernel

theorem tot1784 : totK PD2M8K2 D2M8K2.t1784 = [0, 87578670023, 320896677914, 381564584647, 98918072378, 3462014130, 0, 0] := by
  decide +kernel

theorem rows1785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1785 = true := by
  decide +kernel

theorem tot1785 : totK PD2M8K2 D2M8K2.t1785 = [0, 170369457202, 481090048962, 222972544612, 9707314368, 0, 0, 0] := by
  decide +kernel

theorem rows1786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1786 = true := by
  decide +kernel

theorem tot1786 : totK PD2M8K2 D2M8K2.t1786 = [0, 84245716041, 338990266959, 381085979466, 80848773308, 1198073392, 0, 0] := by
  decide +kernel

theorem rows1787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1787 = true := by
  decide +kernel

theorem tot1787 : totK PD2M8K2 D2M8K2.t1787 = [0, 0, 197483114804, 467885219221, 184332007693, 12052611869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
