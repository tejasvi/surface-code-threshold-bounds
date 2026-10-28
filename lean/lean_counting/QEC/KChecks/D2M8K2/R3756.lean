import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15024 = true := by
  decide +kernel

theorem tot15024 : totK PD2M8K2 D2M8K2.t15024 = [0, 0, 94189627043, 362850316036, 308766160933, 80296644616, 4028038878, 0] := by
  decide +kernel

theorem rows15025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15025 = true := by
  decide +kernel

theorem tot15025 : totK PD2M8K2 D2M8K2.t15025 = [0, 0, 278437249283, 480549353785, 120685742513, 3836120568, 0, 0] := by
  decide +kernel

theorem rows15026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15026 = true := by
  decide +kernel

theorem tot15026 : totK PD2M8K2 D2M8K2.t15026 = [0, 0, 179006250642, 474079453408, 223043596123, 12518069652, 0, 0] := by
  decide +kernel

theorem rows15027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15027 = true := by
  decide +kernel

theorem tot15027 : totK PD2M8K2 D2M8K2.t15027 = [0, 0, 180336160463, 472386011179, 236696601681, 13034811594, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
