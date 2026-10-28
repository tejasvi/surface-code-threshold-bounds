import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3780 = true := by
  decide +kernel

theorem tot3780 : totK PA10K2 A10K2.t3780 = [0, 0, 0, 414316248154, 1613455329659, 2054939645196, 742175672449, 56218611067, 0, 0] := by
  decide +kernel

theorem rows3781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3781 = true := by
  decide +kernel

theorem tot3781 : totK PA10K2 A10K2.t3781 = [0, 0, 0, 442698294714, 1823224307966, 2030922401832, 566541647746, 35693075872, 0, 0] := by
  decide +kernel

theorem rows3782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3782 = true := by
  decide +kernel

theorem tot3782 : totK PA10K2 A10K2.t3782 = [0, 0, 0, 0, 527600637886, 1953554035394, 1721660121584, 409089661047, 25565504801, 0] := by
  decide +kernel

theorem rows3783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3783 = true := by
  decide +kernel

theorem tot3783 : totK PA10K2 A10K2.t3783 = [0, 0, 0, 456920526858, 1652444463572, 1790268118114, 713361334173, 133067826579, 5517381808, 0] := by
  decide +kernel

end QECKChecks.A10K2
