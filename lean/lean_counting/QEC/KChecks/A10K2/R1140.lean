import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4560 = true := by
  decide +kernel

theorem tot4560 : totK PA10K2 A10K2.t4560 = [0, 958173187313, 2383940326752, 1259865295957, 113943173993, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4561 = true := by
  decide +kernel

theorem tot4561 : totK PA10K2 A10K2.t4561 = [0, 460366056830, 1825384814635, 1901818677372, 530504165360, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4562 = true := by
  decide +kernel

theorem tot4562 : totK PA10K2 A10K2.t4562 = [0, 572865945573, 1969589420531, 1853739785285, 420317629987, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4563 = true := by
  decide +kernel

theorem tot4563 : totK PA10K2 A10K2.t4563 = [0, 464615971677, 1773337245648, 1984937074803, 572220263894, 32470943963, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
