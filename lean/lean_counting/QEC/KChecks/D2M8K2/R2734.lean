import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10936 = true := by
  decide +kernel

theorem tot10936 : totK PD2M8K2 D2M8K2.t10936 = [0, 0, 94952814774, 375125459659, 333083859380, 76803717698, 2770420231, 0] := by
  decide +kernel

theorem rows10937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10937 = true := by
  decide +kernel

theorem tot10937 : totK PD2M8K2 D2M8K2.t10937 = [0, 0, 164909182858, 449541421784, 274463413528, 25022329187, 0, 0] := by
  decide +kernel

theorem rows10938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10938 = true := by
  decide +kernel

theorem tot10938 : totK PD2M8K2 D2M8K2.t10938 = [0, 0, 177996210166, 465853886907, 255389510045, 17204625102, 0, 0] := by
  decide +kernel

theorem rows10939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10939 = true := by
  decide +kernel

theorem tot10939 : totK PD2M8K2 D2M8K2.t10939 = [0, 0, 0, 258241782769, 487924545573, 129335360877, 2243379097, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
