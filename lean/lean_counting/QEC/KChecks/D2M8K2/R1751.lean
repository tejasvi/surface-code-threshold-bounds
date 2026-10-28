import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7004 = true := by
  decide +kernel

theorem tot7004 : totK PD2M8K2 D2M8K2.t7004 = [0, 0, 259075824151, 484147634792, 180503471263, 7353292569, 0, 0] := by
  decide +kernel

theorem rows7005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7005 = true := by
  decide +kernel

theorem tot7005 : totK PD2M8K2 D2M8K2.t7005 = [0, 0, 205146316057, 487509204195, 186189056366, 8971621811, 0, 0] := by
  decide +kernel

theorem rows7006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7006 = true := by
  decide +kernel

theorem tot7006 : totK PD2M8K2 D2M8K2.t7006 = [0, 0, 180958268981, 459486529350, 242106792715, 18635025680, 0, 0] := by
  decide +kernel

theorem rows7007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7007 = true := by
  decide +kernel

theorem tot7007 : totK PD2M8K2 D2M8K2.t7007 = [0, 0, 87939979134, 367690863444, 343143911231, 52072694257, 1135526696, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
