import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5972 = true := by
  decide +kernel

theorem tot5972 : totK PD2M8K2 D2M8K2.t5972 = [0, 178282915971, 462112815715, 237133507135, 15585956775, 0, 0, 0] := by
  decide +kernel

theorem rows5973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5973 = true := by
  decide +kernel

theorem tot5973 : totK PD2M8K2 D2M8K2.t5973 = [0, 0, 291239480198, 508569359064, 101683557624, 0, 0, 0] := by
  decide +kernel

theorem rows5974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5974 = true := by
  decide +kernel

theorem tot5974 : totK PD2M8K2 D2M8K2.t5974 = [0, 0, 199841252062, 487249875336, 179357851277, 4627616211, 0, 0] := by
  decide +kernel

theorem rows5975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5975 = true := by
  decide +kernel

theorem tot5975 : totK PD2M8K2 D2M8K2.t5975 = [0, 0, 163748987574, 431698008650, 290805533528, 33047998259, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
